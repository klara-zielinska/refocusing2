
Class CompPred U (P : U -> Prop) :=
{ satisfyingness_comp : forall x, {P x} + {~P x} }.


Definition is_satisfied {U} P `{CompPred U P} x := satisfyingness_comp x.


Definition satisfied {U} P `{CompPred U P} x : Prop :=
    if is_satisfied P x then True else False.


Definition subset {U} P `{CompPred U P} := { x : U | satisfied P x }.

Notation "x ? P " := (satisfied P x) (no associativity, at level 89).
Notation "{? U | P }" := (@subset U P _) (U at level 0).
Notation "¹ x" := (proj1_sig x) (at level 0).
(* Bad without eta_CompPred :
Notation "{ x : U |? P }" := (@subset U (fun x => P) _). *)



Definition sat_token                                          {U} P `{CompPred U P} {x} :
    P x -> x ? P :=

    fun H0 => match is_satisfied P x as s
              return (if s then True else False) : Prop
              with
              | left _ => I
              | right notH0 => notH0 H0 
              end.

Definition sat_untoken                                          {U} P `{CompPred U P} x :
    x ? P -> P x :=

    fun W  => match is_satisfied P x as s 
              return ((if s then True else False) : Prop) -> _ 
              with
              | left H      => fun _ => H
              | right notH0 => fun devil => match devil with end
              end W.

Notation "H '`as' 'witness' 'of' P" := (sat_token P H) (no associativity, at level 73).
Notation "W '`as' 'proof' 'of' P"   := (sat_untoken P W) (no associativity, at level 73).



Instance not_CompPred                                                             {U} P :
    CompPred U P -> CompPred U (fun x => ~P x) :=

{
    satisfyingness_comp := fun x =>
        match is_satisfied P x with
        | left H  => right (fun notH => notH H)
        | right H => left H
        end
}.


Instance const_CompPred                                                          {U1} P :
    CompPred U1 P -> forall U2 x,  CompPred U2 (fun _ => P x) :=

{
    satisfyingness_comp := fun _ => is_satisfied P x
}. 


Lemma sat_token_unique :                                  forall {U} P `{CompPred U P} x,
      forall H1 H2 : x ? P, H1 = H2.

Proof.
  intros U P H x H1 H2.
  unfold satisfied in *.
  destruct (is_satisfied P x);
  solve [destruct H1, H2; auto].
Qed.


Hint Resolve sat_token sat_token_unique.


(*
Instance eta_CompPred {U} P {H : CompPred U P} : CompPred U (fun x => P x) := H.
*)

(*
Instance strange_CompPred {U} P {H : CompPred U P} : CompPred U P := H.
*)

(*
Definition P (x : unit) := True.


Instance udp : CompPred unit P. 
  split; unfold P; auto. Defined.


Definition S1 := subset (fun (x : unit) => P x).
Definition S2 := subset (fun (x : unit) => ~True).
*)