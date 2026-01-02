(* 

  Axel van Abkoude - s1021909
  Project 4

------------------------------------------------
4 Proving an expression compiler correct
Formalize both an interpreter and a compiler for a simple language of arith-
metical expressions, and show that both give the same results. Compile the
expressions to code for a simple stack machine. Use dependent types to make
Rocq aware of the fact that the compiled code will never lead to a run time error.

 *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.

(*
Inductive definition:
 *)

Definition lit := nat. 
Definition binop := (lit -> lit -> lit). 

(*Partial map*)
(*
Definition env := string -> option lit.
Definition empty : env := (fun _ => None).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then Some l else f y).
 *)

(*Total map: Defaults to 0*)
Definition env := string -> lit.
Definition empty : env := (fun _ => 0).
Definition update (f : env) (x : string) (l : lit) : env :=
  (fun y => if String.eqb x y then l else f y).

Inductive Exp : Set :=
  | Elit : lit -> Exp
  | Evar : string -> Exp
  | Ebinop : binop -> Exp -> Exp -> Exp
.
(*
Semantics for Exp
 *)
Fixpoint eval (e:Exp) (f:env) {struct e} : lit :=
match e with
| Elit l      => l
| Evar x      => f x
| Ebinop op e1 e2 => op (eval e1 f) (eval e2 f)
end.
(*
Definition exp0 := Elit 0.
Definition exp1 := Elit 1.
Definition exp2 := Evar "x".
Definition exp3 := Eplus (Evar "x") (Elit 2).
Definition exp4 := Eplus (Elit 1) (Elit 2).
Definition env0 := update empty "x" 4.
Definition env1 := update env0 "y" 6.
Definition env2 := update empty "y" 6.

Eval compute in (eval exp3 empty).
Eval compute in (eval exp3 env0).
Eval compute in (eval exp3 env1).
Eval compute in (eval exp3 env2).
 *)

(*
Stackbased Implementation 
 *)
 
Inductive RPN : Set :=
  | RPNlit : lit -> RPN
  | RPNvar : string -> RPN
  | RPNbinop : binop -> RPN
.


Fixpoint rpn (e:Exp) {struct e} : list RPN :=
match e with
| Elit l => RPNlit l :: nil
| Evar s => RPNvar s :: nil
| Ebinop op e1 e2 => rpn e1 ++ rpn e2 ++ RPNbinop op :: nil
end.

Fixpoint rpn_eval (inp: list RPN) (stack: list lit) (f : env) {struct inp} : option lit :=
match inp with
| nil => 
  match stack with
  | x::xs => Some x
  | nil  => None
  end
| (RPNlit   l ) :: rs => rpn_eval rs (l  ::stack) f
| (RPNvar   s ) :: rs => rpn_eval rs (f s::stack) f
| (RPNbinop op) :: rs =>
  match stack with
  | x::x'::xs => rpn_eval rs ((op x' x)::xs) f
  | _         => None
  end
end.

Definition rpn0:(list RPN) := (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus)::nil.
Definition rpn1:(list RPN) := (RPNlit 3) :: (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus) :: (RPNbinop plus)::nil.
Definition rpn2:(list RPN) := (RPNlit 3) :: (RPNlit 1) :: (RPNlit 2) :: (RPNbinop plus) :: (RPNbinop mult)::nil.
Eval compute in (rpn_eval (rpn2) nil empty).
Definition rpn3:(list RPN) := (RPNvar "x") :: (RPNlit 2) :: (RPNbinop plus)::nil.
(*
Eval compute in (rpn_eval (rpn3) nil env0).
Eval compute in (rpn_eval (rpn3) nil empty).
 *)

Lemma rpn_applied :
  forall (e : Exp) (f : env) (st : list lit) (code : list RPN),
    rpn_eval (rpn e ++ code) st f =
    rpn_eval code (eval e f :: st) f.
Proof.
  (* We do not need to use a different environment in the induction step*)
  intros e f.
  (* Induction on the expressions*)
  induction e;
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case*)
  - intros st code.
    (* Reshuffle list to get into a form of (rpn e1 ++ (rpn e2 ++ code)) *)
    rewrite <- app_assoc. 
    rewrite <- app_assoc. 
    rewrite <- app_comm_cons. 
    simpl. 
    (* Rewrite the IHs *)
    rewrite IHe1. 
    rewrite IHe2. 
    reflexivity.
Qed.


(*
Prove that
forall e:Exp, Some (eval e) = rpn_eval (rpn e)
 *)
Lemma equivalent_under_extensionality : forall (f:env) (e:Exp), 
  Some (eval e f) = rpn_eval (rpn e) nil f.
Proof.
  intros f e.
  (* Delay the inductive step to the helper Lemma rpn_applied *)
  destruct e; 
  (* Solve trivial cases (Lit and Var) *)
  simpl; try reflexivity.
  (* Solve Binop case by applying the rpn_eval twice*)
  - rewrite rpn_applied.
    rewrite rpn_applied.
    reflexivity.
Qed.

(*
QUESTION:
Discuss how you might avoid explicit consideration of None terms in the
definition of rpn_eval, and explain how you need to modify your formal-
ization in Rocq.

ANSWER:
We can make it a relation which should hold for all Exp. This means that
we do not need to include None terms as we check for all possible expressions,
which can not be None when translated with rpn.

Now if we prove this relation we prove the equivalence, for all values that 
an Expression can have.
 *)
