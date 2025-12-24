(*
  ============================================================
  diagrams_equiv.v
  ============================================================

  This file is intentionally SIMPLE.

  Goal:
    Model the idea that two Feynman-like diagrams are
    "physically equivalent" if they produce the same
    observable outcome (same amplitude).

  We DO NOT attempt to prove deep structural theorems.
  Instead, we define equivalence at the observable level.

  Think "API contract", not "implementation details".

  Audience:
    - CS background
    - Lay familiarity with physics and HoTT ideas
    - No advanced category theory or QFT required
*)

(* ------------------------------------------------------------ *)
(* Imports                                                      *)
(* ------------------------------------------------------------ *)

Require Import List.
Import ListNotations.

(* ------------------------------------------------------------ *)
(* 1. A toy data type for "diagrams"                            *)
(* ------------------------------------------------------------ *)

(*
  Think of this as a VERY simplified Feynman diagram.

  - Leaf n       : an external leg / particle labeled by n
  - Node d1 d2   : composition of two subdiagrams

  This is just a binary tree.
*)
Inductive Diagram : Type :=
| Leaf : nat -> Diagram
| Node : Diagram -> Diagram -> Diagram.

(* ------------------------------------------------------------ *)
(* 2. Observable: "leaves"                                      *)
(* ------------------------------------------------------------ *)

(*
  leaves : Diagram -> list nat

  This function extracts the "observable content" of a diagram.

  Physics intuition:
    - Leaves correspond to external particles
    - The list of leaves corresponds to the amplitude inputs

  CS intuition:
    - This is the PUBLIC API
    - Internal structure is private implementation detail
*)
Fixpoint leaves (d : Diagram) : list nat :=
  match d with
  | Leaf n => [n]
  | Node d1 d2 => leaves d1 ++ leaves d2
  end.

(* ------------------------------------------------------------ *)
(* 3. Print / inspect example (interactive use)                 *)
(* ------------------------------------------------------------ *)

(*
  This is NOT a runtime print.
  It is evaluated by Coq during interactive stepping.

  To see output:
    - Use CoqIDE
    - Step Forward through this line
*)
Definition example_diagram :=
  Node (Leaf 10) (Node (Leaf 20) (Leaf 30)).

Eval compute in (leaves example_diagram).
(* Expected output:
     = [10; 20; 30] : list nat
*)

(* ------------------------------------------------------------ *)
(* 4. Equivalence = same observable                             *)
(* ------------------------------------------------------------ *)

(*
  This is the KEY DESIGN DECISION.

  Two diagrams are equivalent IF AND ONLY IF
  they have the same observable leaves.

  Physics intuition:
    - Same amplitude
    - Same S-matrix element
    - Same external states

  CS intuition:
    - Observational equivalence
    - Same API output
*)
Definition equiv (d1 d2 : Diagram) : Prop :=
  leaves d1 = leaves d2.

(* ------------------------------------------------------------ *)
(* 5. Two structurally different diagrams                       *)
(* ------------------------------------------------------------ *)

(*
  These diagrams look different internally,
  but should be physically equivalent.
*)

Definition diagram1 :=
  Node (Leaf 1) (Node (Leaf 2) (Leaf 3)).

Definition diagram2 :=
  Node (Node (Leaf 1) (Leaf 2)) (Leaf 3).

(* ------------------------------------------------------------ *)
(* 6. Inspect their observables                                 *)
(* ------------------------------------------------------------ *)

Eval compute in (leaves diagram1).
(* = [1; 2; 3] *)

Eval compute in (leaves diagram2).
(* = [1; 2; 3] *)

(* ------------------------------------------------------------ *)
(* 7. "Unit test": equivalence proof                            *)
(* ------------------------------------------------------------ *)

(*
  This is the Coq equivalent of a unit test.

  Because equiv is DEFINED as equality of leaves,
  and both sides reduce to the same list,
  reflexivity is enough.

  If this compiles, the test passes.
*)
Example diagrams_equiv_test :
  equiv diagram1 diagram2.
Proof.
  reflexivity.
Qed.

(* ------------------------------------------------------------ *)
(* 8. What this file demonstrates                               *)
(* ------------------------------------------------------------ *)

(*
  ✔ We abstracted away internal structure
  ✔ We defined equivalence via observables
  ✔ We avoided fragile inductive proofs
  ✔ We enforced the abstraction with the type system

  This is EXACTLY how one would begin a:
    - HoTT quotient construction
    - Gauge equivalence model
    - Amplitude-level classification
    - Formalization project in a proof assistant

  Future extensions (optional):
    - Add rewrite rules that preserve leaves
    - Define normalization functions
    - Upgrade equiv to HoTT-style paths
    - Replace nat with particle labels
*)
