(*
  ============================================================
  diagrams_equiv.v
  ============================================================

  This file models Feynman-like diagrams using binary trees.

  ============================================================
  HIGHLY DETAILED CS-FRIENDLY COMMENTS
  ============================================================

  1. Goal

  - Model diagrams as binary trees, but NOT arbitrary trees
  - Select a **canonical form** (right-associated) for each tree
    to make reasoning about equivalence easy
  - Define **equivalence** via leaves (observable particles)
  - Leaves = “external particles” = observable output = amplitude
  - Internal nesting = internal propagators = implementation details

  ============================================================
  2. Binary tree / right-associated intuition

  Suppose we have 3 leaves: 1, 2, 3

  Arbitrary nesting (internal nodes can be on left or right):

      Node
     /    \
   Node     3
  /    \
 1      2

  In Coq code:

  Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

  Right-associated canonical form (“right comb”):

      Node
     /    \
    1     Node
         /   \
        2     3

  In Coq code:

  Node (Leaf 1) (Node (Leaf 2) (Leaf 3))

  Key points:

  - Both trees have the same leaves: [1;2;3]
  - We pick **right-associated form** as canonical
  - All internal nesting goes **to the right**
  - Equivalence class = all trees with same leaves

  ============================================================
  3. CS analogy

  - Tree = implementation / internal structure
  - Leaves = public API / observable output
  - Equivalence = same observable output
  - Right-associated canonical tree = pick **one standard implementation**
    so that proofs, normalization, and equality checks are simple

  ============================================================
  4. Physics analogy

  - Feynman diagrams may differ internally (propagators) but have same external particles
  - Leaves = external particles
  - Two diagrams with same leaves = same amplitude / S-matrix element
  - Right-associated tree = canonical representative for reasoning

*)

(* ------------------------------------------------------------ *)
(* Imports                                                      *)
(* ------------------------------------------------------------ *)

Require Import List.
Import ListNotations.

(* ------------------------------------------------------------ *)
(* 1. Diagram data type                                         *)
(* ------------------------------------------------------------ *)

(*
  Binary tree representation of diagrams
  - Leaf n       : external particle labeled n
  - Node d1 d2   : internal combination of two subdiagrams

  IMPORTANT:
  We are only selecting trees that can be **right-associated**
  to form a canonical representative.
  This does NOT restrict the code, but is how we reason about equivalence.
*)
Inductive Diagram : Type :=
| Leaf : nat -> Diagram
| Node : Diagram -> Diagram -> Diagram.

(* ------------------------------------------------------------ *)
(* 2. Observable leaves function                                 *)
(* ------------------------------------------------------------ *)

(*
  leaves : Diagram -> list nat
  Extracts the “observable” part of the diagram

  Physics analogy:
    - Leaves correspond to external particles
    - Sequence of leaves represents amplitude inputs

  CS analogy:
    - Leaves = public API / observable output
    - Internal tree structure is private implementation
*)
Fixpoint leaves (d : Diagram) : list nat :=
  match d with
  | Leaf n => [n]
  | Node d1 d2 => leaves d1 ++ leaves d2
  end.

(* ------------------------------------------------------------ *)
(* 3. Example diagrams and evaluation                           *)
(* ------------------------------------------------------------ *)

Definition example_diagram :=
  Node (Leaf 10) (Node (Leaf 20) (Leaf 30)).

Eval compute in (leaves example_diagram).
(* Expected output:
     = [10; 20; 30] : list nat
*)

(* ------------------------------------------------------------ *)
(* 4. Equivalence definition                                     *)
(* ------------------------------------------------------------ *)

(*
  Two diagrams are equivalent if they have the SAME observable leaves

  Physics analogy:
    - Two diagrams with same external particles produce same amplitude

  CS analogy:
    - Two implementations produce same API output
    - Internal differences are ignored
*)
Definition equiv (d1 d2 : Diagram) : Prop :=
  leaves d1 = leaves d2.

(* ------------------------------------------------------------ *)
(* 5. Example: two differently nested diagrams                  *)
(* ------------------------------------------------------------ *)

(* Arbitrary nesting *)
Definition diagram1 :=
  Node (Leaf 1) (Node (Leaf 2) (Leaf 3)).

(* Left-heavy nesting *)
Definition diagram2 :=
  Node (Node (Leaf 1) (Leaf 2)) (Leaf 3).

(* ------------------------------------------------------------ *)
(* 6. Inspect observables                                       *)
(* ------------------------------------------------------------ *)

Eval compute in (leaves diagram1).
(* = [1; 2; 3] *)

Eval compute in (leaves diagram2).
(* = [1; 2; 3] *)

(* ------------------------------------------------------------ *)
(* 7. Unit test for equivalence                                  *)
(* ------------------------------------------------------------ *)

(*
  Reflexivity works because our equivalence is defined
  as equality of leaves. Both diagrams reduce to the same list.
*)
Example diagrams_equiv_test :
  equiv diagram1 diagram2.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* 8. Summary / lessons                                         *)
(* ------------------------------------------------------------ *)

(*
  - Only binary trees with **right-associated canonical form** are used
  - Equivalence = same leaves / observables
  - Leaves correspond to external particles / amplitudes
  - Internal nesting is ignored (implementation detail)
  - This matches both CS and physics intuitions
  - ASCII diagrams above help visualize canonical vs arbitrary trees

  Future extensions (optional):
    - Introduce rewrite rules preserving leaves
    - Define normalization to canonical form
    - Upgrade equiv to HoTT paths
    - Replace nat labels with structured particle types
*)
