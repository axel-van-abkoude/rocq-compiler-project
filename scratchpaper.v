

(*
Conveluted Stackbased Implementation 
 
Inductive RPN' : Set :=
  | RPNlit' : lit -> RPN'
  | RPNvar' : string -> RPN'
  | RPNbinop' : (lit -> lit -> lit) -> RPN'
.
Fixpoint rpn' (e:Exp) {struct e} : list RPN' :=
match e with
| Elit l => RPNlit' l :: nil
| Evar x => RPNvar' x :: nil
| Eplus e1 e2 => rpn' e1 ++ rpn' e2 ++ RPNbinop' plus :: nil
| Emin  e1 e2 => rpn' e1 ++ rpn' e2 ++ RPNbinop' min  :: nil
| Emult e1 e2 => rpn' e1 ++ rpn' e2 ++ RPNbinop' mult :: nil
end.
Fixpoint rpn_eval' (inp: list RPN') (stack: list lit) (f : env) {struct inp} : option (list lit) :=
match inp with
| nil => Some stack
| r::rs =>
  match r with
  | RPNlit' l => rpn_eval' rs (l::stack) f
  | RPNvar' x => 
    match f x with
    | Some l  => rpn_eval' rs (l::stack) f
    | _       => None
    end
  | RPNbinop' op =>
    match stack with
    | x::x'::xs => rpn_eval' rs ((op x x')::xs) f
    | _ => None
    end
  end
end.

Lemma Equivalence_Eval_RPNEval' : forall e:Exp, eval e = rpn_eval' (rpn' e) nil.
Proof.
  induction e; simpl; try rewrite <- IHe1, <- IHe2; reflexivity.
Qed.


Definition rpn0':(list RPN') := (RPNlit' 1) :: (RPNlit' 2) :: (RPNbinop' plus)::nil.
Eval compute in (rpn_eval' (rpn0') nil empty).
Definition rpn1':(list RPN') := (RPNvar' "x") :: (RPNlit' 2) :: (RPNbinop' plus)::nil.
Definition env0' := update empty "x" 4.
Definition env1' := update env0 "y" 6.
Eval compute in (rpn_eval' (rpn1') nil env0').
Eval compute in (rpn_eval' (rpn1') nil empty).

 *)
