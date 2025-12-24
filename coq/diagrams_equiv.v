(*
  ============================================================
  diagrams_equiv.v
  ============================================================

  🎸 Channeling Jack Black: This is Just a Tribute 🎸

  Inspired by Jack Black’s “Greatest Song in the World,” this Coq code is
  not a full twistor string theory Feynman diagram model in HoTT, but a
  playful toy tribute / starting point.

  ============================================================
  1. Goal

  - Model Feynman-like diagrams as binary trees, but **only consider
    right-associated canonical trees**.
    - Right-associated = all internal nodes nested to the right
    - Arbitrary trees must first be normalized to right-associated form
      before checking equivalence
  - Define equivalence using **observable leaves** (external particles / amplitudes)
  - Allow multiple different internal structures (diagrams) to be
    treated as equivalent if they yield the same observable leaves

  Physics analogy:
    - Two diagrams with different intermediate states (internal nodes)
      may produce the same final external particles (leaves)
    - Leaves correspond to observable final states and amplitude

  CS analogy:
    - Tree = implementation / internal structure
    - Leaves = public API output / observable output
    - Equivalence = same observable output
    - Right-associated tree = canonical implementation for simplicity

  ============================================================
  2. Binary tree / right-associated intuition

  Suppose we have 3 leaves: 1, 2, 3

  Arbitrary nesting (not canonical):

        Node
       /    \
     Node     3
    /    \
   1      2

  Right-associated canonical form:

        Node
       /    \
      1     Node
           /   \
          2     3

  - Both trees have the same leaves: [1;2;3]
  - Only right-associated trees are considered for equivalence
  - Leaves order is preserved; internal node grouping may differ

  ------------------------------------------------------------
  Example physics analogy: meson decay

  Diagram 1:                 Diagram 2:
       M                          M
      / \                        / \
     A   B                      X   Y
    / \                            \
   e   e                            e

  - Both produce final electrons (leaves = [e,e])
  - Internal structure differs
  - In our toy model, these diagrams are equivalent

*)

(* ------------------------------------------------------------ *)
(* Imports                                                      *)
(* ------------------------------------------------------------ *)

Require Import List.
Require Import String.
Open Scope string_scope.
Import ListNotations.

(* ------------------------------------------------------------ *)
(* 1. Diagram data type                                         *)
(* ------------------------------------------------------------ *)

Inductive Diagram : Type :=
| Leaf : nat -> Diagram
| Node : Diagram -> Diagram -> Diagram.

(* ------------------------------------------------------------ *)
(* 2. Observable leaves function                                 *)
(* ------------------------------------------------------------ *)

Fixpoint leaves (d : Diagram) : list nat :=
  match d with
  | Leaf n => [n]
  | Node d1 d2 => leaves d1 ++ leaves d2
  end.

(* ------------------------------------------------------------ *)
(* 3. Equivalence definition                                     *)
(* ------------------------------------------------------------ *)

Definition equiv (d1 d2 : Diagram) : Prop :=
  leaves d1 = leaves d2.

(* ------------------------------------------------------------ *)
(* 4. Example diagrams                                           *)
(* ------------------------------------------------------------ *)

Definition diagram1 :=
  Node (Leaf 1) (Node (Leaf 2) (Leaf 3)).

Definition diagram2 :=
  Node (Node (Leaf 1) (Leaf 2)) (Leaf 3).

(* ------------------------------------------------------------ *)
(* 5. Unit test                                                  *)
(* ------------------------------------------------------------ *)

Example diagrams_equiv_test :
  equiv diagram1 diagram2.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* 6. ASCII tree printer                                         *)
(* ------------------------------------------------------------ *)

(*
  Tiny ASCII printer for diagrams
  - Visualizes binary tree structure
  - Right-associated trees show clearly as “right combs”
*)

Fixpoint show_diagram_aux (d : Diagram) (indent : string) : list string :=
  match d with
  | Leaf n => [indent ++ "Leaf " ++ (string_of_nat n)]
  | Node l r =>
      let this := [indent ++ "Node"] in
      this ++ (show_diagram_aux l (indent ++ "  ")) ++ (show_diagram_aux r (indent ++ "  "))
  end

with string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | S n' => string_of_nat_aux n' 1
  end

with string_of_nat_aux (n : nat) (acc : nat) : string :=
  match n with
  | O => string_of_nat_nat acc
  | S n' => string_of_nat_aux n' (S acc)
  end

with string_of_nat_nat (n : nat) : string :=
  match n with
  | O => "0"
  | S n' =>
      let rec := string_of_nat_nat n' in
      append "1" rec (* crude, just to see distinct leaves *)
  end.

Definition show_diagram (d : Diagram) : list string :=
  show_diagram_aux d "".

(* Example usage: *)

Eval compute in (show_diagram diagram1).
Eval compute in (show_diagram diagram2).

(* Each Eval compute prints a list of strings representing the tree.
   Right-associated forms are visually apparent as nested right nodes. *)
