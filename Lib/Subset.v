


Class CompPred (U : Type) (P : U -> Prop) : Type :=
{ satisfyingness_comp : forall x, {P x} + {~P x} }.


Definition is_satisfied {U} P `{CompPred U P} x :=
    satisfyingness_comp x.


Definition satisfied {U} P `{CompPred U P} x : Prop :=
    if is_satisfied P x then True else False.


Definition subset {U : Set} (P : U -> Prop) `{CompPred U P} :=
    { x : U | satisfied P x }.
Definition subtype {U : Type} (P : U -> Prop) `{CompPred U P} :=
    { x : U | satisfied P x }.


Notation "x ? P"       := (satisfied P x)                (no associativity, at level 89).
Notation "{S? U | P }" := (@subset U P _).
Notation "{T? U | P }" := (@subtype U P _).
Notation "x ?& W"      := (exist _ x W)                  (no associativity, at level 89).
Notation "¹ x"         := (proj1_sig x)                                     (at level 0).
Notation "² x"         := (proj2_sig x)                                     (at level 0).
(* Bad without eta_CompPred :
Notation "{S? x : U | P }" := (@subset  U (fun x => P) _).
Notation "{T? x : U | P }" := (@subtype U (fun x => P) _). *)


Definition submember                                        {U : Set} P `{CompPred U P} :
    forall x, satisfied P x -> subset P :=

    fun x H => x ?& H.

Definition submemberT                                      {U : Type} P `{CompPred U P} :
    forall x, satisfied P x -> subtype P :=

    fun x H => x ?& H.


Definition witness_intro                                        {U} P `{CompPred U P} x :
    P x -> x ? P :=

    fun H0 => match is_satisfied P x as s
              return (if s then True else False) : Prop
              with
              | left _ => I
              | right notH0 => notH0 H0 
              end.


Definition witness_elim                                         {U} P `{CompPred U P} x :
    x ? P -> P x :=

    fun W  => match is_satisfied P x as s 
              return ((if s then True else False) : Prop) -> _ 
              with
              | left H      => fun _ => H
              | right notH0 => fun devil => match devil with end
              end W.


Notation "H '`as' 'witness' 'of' P x" := (witness_intro P x H)         (no associativity,
                                                              at level 73, P at level 0).
Notation "W '`as' 'proof' 'of' P x"   := (witness_elim P x W)          (no associativity,
                                                              at level 73, P at level 0).



Definition submember_by                                     {U : Set} P `{CompPred U P} :
    forall x, P x -> subset P :=

    fun x H => submember P x (H `as witness of P x).

Definition submemberT_by                                   {U : Type} P `{CompPred U P} :
    forall x, P x -> subtype P :=

    fun x H => submemberT P x (H `as witness of P _).



Instance not_CompPred                                                             {U} P :
    CompPred U P -> CompPred U (fun x => ~P x) :=

{
    satisfyingness_comp := fun x =>
        match is_satisfied P x with
        | left H  => right (fun notH => notH H)
        | right H => left H
        end
}.



Instance const_CompPred                                                     {U1} P U2 x :
    CompPred U1 P -> CompPred U2 (fun _ => P x) :=

{
    satisfyingness_comp := fun _ => is_satisfied P x
}.


(*
Instance eta_CompPred                                                             {U} P :
    CompPred U P -> CompPred U (fun x => P x) :=

    fun H => H.

Definition instantiation_loop U P (H : CompPred U P) x := 
    is_satisfied (fun x => ~P x) x.
*)



Lemma witness_unique :                                    forall {U} P `{CompPred U P} x,
      forall H1 H2 : x ? P, H1 = H2.

Proof.
  intros U P H x H1 H2.
  unfold satisfied in *.
  destruct (is_satisfied P x);
  solve [destruct H1, H2; auto].
Qed.


Hint Resolve witness_intro witness_unique.

